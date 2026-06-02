# ATLAS axiom / sorry audit

`atlas_audit` is a standalone Lean executable that reports, for every
declaration defined in an `Atlas.*` module, whether the Lean kernel considers
it actually proved.

It walks each declaration's transitive axiom dependencies (the same traversal
`#print axioms` uses) and classifies it:

| Status        | Meaning |
|---------------|---------|
| `proved`      | Depends only on the benign classical axioms `propext`, `Classical.choice`, `Quot.sound`. |
| `sorry`       | Transitively depends on `sorryAx`, i.e. some step is an unfilled `sorry`. |
| `other-axiom` | Depends on another axiom (including any declared with `axiom`). Surfaced for review. |

This is complementary to the `proof_integrity` field in each book's
`report.json`: that score is produced by an LLM judge, while this audit is
computed from the kernel's own dependency tracking, so it is ground truth
about what is proved.

## Running

```bash
lake build Atlas        # the audit loads compiled Atlas oleans at runtime
lake exe atlas_audit    # writes audit/proved.json, prints a per-book summary
```

Optional arguments:

- a positional output directory (default `audit`), e.g. `lake exe atlas_audit out`;
- `--strict`: exit non-zero if any declaration depends on a non-benign,
  non-`sorry` axiom. Useful as a CI gate once the corpus has a known axiom
  baseline.

`atlas_audit` itself imports only `Lean`, so `lake build atlas_audit` compiles
without building Mathlib or Atlas. The libraries are needed only at run time.

## Output

`audit/proved.json`:

```json
{
  "generated_by": "atlas_audit",
  "benign_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "summary": { "proved": 0, "sorry": 0, "other_axiom": 0 },
  "books": [ { "book": "RealAnalysis", "proved": 0, "sorry": 0, "other_axiom": 0, "total": 0 } ],
  "declarations": [
    { "declaration": "...", "book": "...", "module": "...", "status": "proved", "axioms": ["propext"] }
  ]
}
```

CI runs the audit on every push and pull request (see
`.github/workflows/audit.yml`) and uploads `proved.json` as an artifact.
