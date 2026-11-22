# AlgebraNotes migration ledger

`AlgebraNotes.json` is the first book's compact source-to-library ledger, not
another inventory generator, a second blueprint, or a completed migration.
It binds all 176 archived targets at base
`8de8f74fa5760eb8b768a9804494ca2ab631cf87` without copying their descriptions,
report prose, or Lean proofs. It adds no source library and leaves v1 unchanged.

## Format (`algebra-notes-migration/1`)

- `sources` pins the target/report paths, Git blobs, byte counts and SHA-256s.
  `pins` records Mathlib and the repository Lean toolchain.
- Each `records` entry has a **zero-based ordinal + sourceHash**. `sourceHash`
  is inventory_v1's canonical hash of the four decoded target fields, not a
  declaration hash or printed-source hash. Duplicate targets retain separate
  ordinals. The real input has 176 distinct hashes; duplicate fixtures are tested.
- `legacy_matches` preserves every report-row ordinal/hash and its independent
  declaration-name and file-hint lists. Names are never zipped with files.
  Repeated declarations remain separate occurrences: 166 references to 156
  distinct names. File hints do not prove where a name is defined.
- `legacy_declarations` holds 266 named declarations from the prior static
  audit, including helpers not directly named by the report. File blobs and
  `historical_excerpt_sha256` are references, not retained Lean. `finding` and
  `historical_hole_dependencies` are historical observations, never compiler
  dependency or axiom evidence. Even `mapped_existing` is only an old candidate.
- `destination_apis` names exact API/module/revision candidates by prior audit
  receipt ID. There are 107 mapping pointers (97 distinct API/module/pin tuples):
  104 replacement candidates and 3 related candidates. Every mapping has
  `scope: unverified`; `static_shape_only` and `partial_bridge_unverified` explain
  its limit. No target scope is inferred from the containing file's compilation.
- `prior_audit` hashes locate the supplied audit inputs; these inputs are not
  shipped or treated as acceptance. The validator does not reconstruct them.

Target dispositions are non-acceptance labels. `static_candidate` requires only
historical replacement candidates and no inventory gaps; `unresolved` keeps
unknown scope/API work explicit. `partial_source` records missing or mismatched
report metadata. `blocked_false`, `blocked_sorry`, `blocked_semantics`, and
`blocked_parallel` preserve adverse historical findings. `reasons` retains
inventory gap codes and the applicable disposition reason; a blocking finding
can coexist with metadata gaps. These labels neither establish nor refute the
printed textbook claim.

## Validation

Use Python 3.11+ and the existing `scripts/requirements-inventory.txt` dependency.
From the root:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s scripts -p test_algebra_notes_migration.py -v
python3 scripts/check_algebra_notes_migration.py
```

The validator calls PR #202's `inventory_v1.book_inventory`, safe parsers and
canonical hash helpers. It checks populated, complete unique ordinal/hash
coverage, exact source/report fingerprints and report joins, legacy file blobs,
reference binding, destination/toolchain pins, explicit statuses and reasons.
It rejects extra evidence/badge fields and misleading promotions. Tests use
invented fixtures, including duplicate targets/declarations and failures for
missing, duplicate, out-of-range, stale and unbound records.

The default reads the frozen base object. Shallow CI passes
`--source-revision HEAD`: it compares the candidate tree's metadata fingerprints
and pins to this frozen ledger without fetching history. This is an identity
check, not an ancestry/full-tree guard; those guards remain parent-owned.

## Unverified boundary

`migration` remains `partial`. Printed-source fidelity is unverified with
`sha256: null`: canonical OCW access was policy-denied and no primary bytes were
supplied. Source text identity is not formal source fidelity. Compiler-use tests,
formal equivalence and semantic review are separate parent-owned pending gates.
Historical compilation/pass/axiom claims are not consumed as proof evidence.

`proof_receipts` is explicitly empty. The historical ledger admits no accepted
migration proof receipts or checked/accepted target statuses. Fresh triage and
canonical-use byte identities live in the separate index below; they do not
promote the historical `mapped_existing` findings.

## Fresh triage and canonical-use index

`AlgebraNotesChecks.json` (schema `algebra-notes-checks/2`) is a compact
companion to this same book ledger. Its `identity_sha256` binds the
book/base/source fingerprints/library pins. Each `row_content_sha256` is the
canonical SHA-256 of that row's other committed fields. The three
`triage_sources` content fingerprints are likewise recomputed by the validator
from the committed lane rows: the full triage-row contents sorted by ordinal,
the ordinal/legacy-declaration pairs, and the API-row contents sorted by ID.
These content hashes make the committed triage transcription tamper-evident;
they do not prove its fidelity to the supplied lane maps, which are not
committed, so transcription fidelity remains unverified. `triage` joins each
fresh observation by lane, ordinal and authoritative sourceHash.
`triage_apis` provides exact named API/module/pin pointers; unresolved
anonymous instance names remain explicitly null.

Fresh dispositions are triage only. Every source remains unverified; scope
issues have compact codes and `scope: partial`, never complete-clause coverage.
Validation requires the declared triage API IDs to be exactly those referenced
by triage rows, so stale or unrelated API rows cannot hide in the index.
The two lanes account for 174 targets (107 foundations, 67 linear). Explicit
`pending_targets` retains ordinals 34 and 158 with missing context, and validation
requires fresh triage plus pending targets to cover all 176 identities.
The historical ledger and its prior_audit hashes remain unchanged.

Each `canonical_use_tests` entry names an actual `MathlibExtTest` file/SHA-256
and only the intended target/sourceHash/API bindings. Its example IDs identify
exact byte ranges and hashes in that file, not compiler-resolved declarations.
A byte span or lexical match is **not proof evidence**. The validator rejects
missing/stale files, spans, target/API joins, duplicate bindings and overclaims.
Intended API use and the span's relationship to the target require parent review;
byte identity alone cannot establish either.
Every indexed test has `scope: canonical_use_only` and unverified source fidelity.
Compiler evidence in this index is always `parent_pending`, with no receipt or
environment, and `compiler_environments` is empty. No reproducible receipt
artifact binding a test file, compiler environment, command, and successful
result is committed, so the validator counts zero reported compiles and rejects
any stronger compiler-evidence claim. Repository CI and local Lean builds are
separate execution gates; their results are not recorded as receipts here.

Successful canonical-use compilation cannot pass the separate migration/v1
compiler gates, prove formal equivalence, or establish printed-source fidelity.
Those gates remain pending even where an indexed canonical-use test passes.
Each bound example has explicit partial scope and a component, boundary or
compatibility reason; no whole-source coverage is inferred from a passing file.
All 18 parent-copied test file hashes are retained with only meaningful bindings.
Examples lacking a matching target/API pointer remain unbound/pending in the
local handoff rather than receiving invented receipts. Source, v1 equivalence
and exact destination-environment gates remain independently pending.
