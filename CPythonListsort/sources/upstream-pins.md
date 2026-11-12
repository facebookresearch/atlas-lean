# Pinned upstream revisions and checksums

These immutable revisions define the source and tooling snapshot used by the
project.

## CPython

- Repository: [`python/cpython`](https://github.com/python/cpython)
- Selection rule: latest `main` snapshot resolved at source-corpus creation
- Full commit: [`67e6be72be9c0b75a31795ed42f9afb5eb431d47`](https://github.com/python/cpython/commit/67e6be72be9c0b75a31795ed42f9afb5eb431d47)
- `Objects/listobject.c` SHA-256: `ae082e295971b1c7cd2156d43421be07c6f4faf5fdf3577c695de22dcc564432`
- `Objects/listsort.txt` SHA-256: `674d514b968e2a9b6f785ca2cbd99e09edc63bbc0f3698033391c27f53757512`

The branch name chose the snapshot only. All downloads, citations, line ranges,
and verification use the full commit rather than the moving branch.

## Development formalization

- Repository: [`neelsomani/cpython-listsort-lean`](https://github.com/neelsomani/cpython-listsort-lean)
- Exported commit:
  [`7a5f47de2501d41980fafa0a363c61c2a2fa688c`](https://github.com/neelsomani/cpython-listsort-lean/commit/7a5f47de2501d41980fafa0a363c61c2a2fa688c)

The Lean sources, source notes, and roadmap in this entry are an export of that
merged development-repository snapshot, with module imports rewritten from
`CPythonListsort.*` to `Code.*`; declaration namespaces are unchanged.

## Munro-Wild paper

- J. Ian Munro and Sebastian Wild, *Nearly-Optimal Mergesorts: Fast,
  Practical Sorting Methods That Optimally Adapt to Existing Runs*
- arXiv: [`1805.04154v1`](https://arxiv.org/abs/1805.04154v1), 10 May 2018
- Local pinned PDF: [munro-wild-powersort.pdf](munro-wild-powersort.pdf)
- SHA-256: `edf79f9d25bb654edcc631b0b7883e0a37140a3674556f16382fab100ddeb54b`

## Tooling

- Lean: `v4.33.1`
- Mathlib: `v4.33.1`, resolved to commit
  `0df444a360eaa60ab8c11dca51a86af692955474`
- AutoformBot: [`13be889dee8477cba7271d3b805c5a87460124a3`](https://github.com/facebookresearch/autoform-bot/commit/13be889dee8477cba7271d3b805c5a87460124a3)

`verify/verify_excerpts.py` re-downloads both CPython files through the pinned
commit and checks the generated Markdown byte-for-byte.
