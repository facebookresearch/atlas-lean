---
name: atlas-solve-issue
description: >-
  Pick up an ATLAS task issue (task:formalize or task:dag-work), take it, do
  the work, open a PR that closes it, and carry the PR through Codex and human
  review to merge. Use when asked to "work on ATLAS", "solve an issue", or
  "pick up a task" in facebookresearch/atlas-lean.
---

# Solve an ATLAS task issue

Task issues are the graph's frontier: each one can start now, because
nothing it needs is unfinished. They are opened and closed automatically from
the graph on `main`, so don't open or close them by hand.

| Label | Work | How |
| --- | --- | --- |
| `task:formalize` | One field's ready results, grouped by Lean module: write their statements in Lean, or prove the stated ones | This skill, then [REVIEWING.md](../../../REVIEWING.md) |
| `task:dag-work` | Break a node marked unexpanded into children | This skill, then [atlas-graph-pr](../atlas-graph-pr/SKILL.md) |

## 1. Pick an issue

```sh
gh issue list -R facebookresearch/atlas-lean --label task:formalize --search "no:assignee" --limit 20
```

- Prefer an issue in an area you know, and one whose page states the result
  precisely.
- Read the whole issue: the page link, the Lean declaration, its
  dependencies and the acceptance criteria.
- Skip an issue with an open PR already linked.

## 2. Claim it

Comment `/claim` on the issue before you start, and on a field issue name the
module you take (`/claim` then, on the next line, `Taking <module>`). A bot
assigns you, or says who already holds the task; a field issue takes several
holders, one module each, so check the earlier claims first. Work one issue at a time unless you are asked to
batch:

```sh
gh issue comment <number> -R facebookresearch/atlas-lean --body /claim
```

Open a draft PR that references the issue early: a claim lapses after seven
days without an open PR that references it. If you stop without a PR, comment
`/unclaim` so someone else can take it. A maintainer can free a stalled task
with `/unclaim @someone`.

## 3. Do the work

For `task:formalize`, the issue lists every ready result of one field,
grouped by Lean module, as a checklist. Take one module of the list (or part
of a large one) per PR; claim the issue while you work, and say
`Part of #<issue>` in the PR. The list updates itself after each merge, and
the issue closes when nothing in the field is ready. For each result:

- **Proving a `theorem_wanted`:** move the result to the matching proved
  library (`MathlibExt`, `CSLibExt` or `PhyslibExt`), as
  [WantedExt/README.md](../../../WantedExt/README.md) says. State it exactly
  as the wanted statement does, prove it, and end its docstring with
  ``Proves `Wanted` entry `<name>`.``. Remove the `theorem_wanted`. In the
  article's annotation in `blueprint/links/<Subject>.jsonl`, change the
  `declaration` to the proved name, so the page follows the result rather
  than becoming a duplicate.
- **Writing a `def_wanted`:** give the definition in the proved library in the
  same way, with focused tests in the matching `*Test` library.
- The statement must match the page and its source clause by clause.
  `REVIEWING.md` lists what reviewers check: faithfulness, Mathlib API use,
  tests, copyright headers (`CONTRIBUTING.md`), and no `sorry`, axioms or
  `native_decide`.
- Search pinned Mathlib and the repository before writing a helper. Reuse
  beats a parallel encoding.

For `task:dag-work`, follow [atlas-graph-pr](../atlas-graph-pr/SKILL.md).

Check before you open the PR:

```sh
lake build <changed modules>
scripts/check.sh
python scripts/check_graph_rules.py --base origin/main   # if blueprint/ changed
```

## 4. Open the PR

- Push to your fork, and open the PR against `main` on
  facebookresearch/atlas-lean.
- Fill in `.github/pull_request_template.md`. The body says
  `Part of #<issue>` for a field issue (`Closes #<issue>` for a node to
  expand), the
  declarations added or moved, and the source.
- One issue per PR.

## 5. See it through to merge

- Codex reviews every PR automatically and posts a verdict. Address each
  finding: fix it and push, or reply with evidence that it does not apply.
  Comment `@codex` to ask it a question or to re-review.
- Fix failing CI before asking for human review. Rebase when `main` moves
  under you.
- A human maintainer merges. A PR that touches the graph also needs a code
  owner's approval.
- When the PR merges, the issue closes, and the next frontier run opens the
  issues that this result unblocked.
