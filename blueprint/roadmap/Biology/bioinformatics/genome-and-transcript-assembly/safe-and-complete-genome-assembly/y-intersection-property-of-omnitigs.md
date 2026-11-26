# Y-intersection property of omnitigs

**Setting.** Let $G$ be a strongly connected directed graph that is not a single closed path. An arc is a *join* arc if its head has in-degree at least two and a *split* arc if its tail has out-degree at least two; two arcs are *siblings* if they share their tail (split arcs) or their head (join arcs). A walk is *join-free* (*split-free*) if none of its arcs is a join (split) arc. Omnitigs are as in [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md).

**Theorem (Cairo–Rizzi–Tomescu–Zirondelli).** Let $fWg$ be an omnitig of $G$, where $f$ is a join arc and $g$ is a split arc.

1. If $W$ is a join-free path (possibly empty), then $fWg'$ is not an omnitig for any sibling split arc $g'\ne g$ of $g$.
2. If $W$ is a split-free path (possibly empty), then $f'Wg$ is not an omnitig for any sibling join arc $f'\ne f$ of $f$.

## Depends on

- [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)

## Proof depends on

- [Extension property of omnitigs](extension-property-of-omnitigs.md)

## Expansion

For join-free $W$ the extension property says that $fWg$ is an omnitig exactly when $g$ is the unique arc out of $h(W)$ whose head reaches $h(f)$ in $G\setminus f$; uniqueness rules out every sibling $g'$. The second item is the same argument in the reverse graph, where omnitigs are reversed omnitigs and join and split arcs swap roles.

## Sources

- Massimo Cairo, Romeo Rizzi, Alexandru I. Tomescu and Elia C. Zirondelli, "Genome assembly, from practice to theory: safe, complete and linear-time", arXiv:2002.10498 (2020); published in ICALP 2021, LIPIcs 198, paper 43, <https://doi.org/10.4230/LIPIcs.ICALP.2021.43>; numbering as in the arXiv version: Lemma 16 and Corollary 17 (Y-intersection Property), Section 4.
