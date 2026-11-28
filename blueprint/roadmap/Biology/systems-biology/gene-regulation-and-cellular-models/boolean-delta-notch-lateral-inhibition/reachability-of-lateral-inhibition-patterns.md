# Reachability of lateral-inhibition patterns

In the setting of [Delta–Notch fixed points are minimal vertex covers](delta-notch-fixed-points-are-minimal-vertex-covers.md), let $AD_N$ and $AD_F$ be the asynchronous state transition graphs of the reduced and full Boolean Delta–Notch systems.

**Theorem.**
1. From every non-fixed state of $N$ (resp. $F$) there is a path in $AD_N$ (resp. $AD_F$) to a fixed point; in particular the asynchronous dynamics has no cyclic attractors.
2. Every fixed point of $N$ is reachable from both constant states $\mathbf 1$ and $\mathbf 0$. Every fixed point of $F$ is reachable from any state in which all Notch levels or all Delta levels are equal (all $0$ or all $1$).
3. For $x\in\mathbb B^L$, partition $\{i:x_i=0\}$ into the maximal subsets $I_\nu$ inducing connected subgraphs of $\mathcal G$. A fixed point $y$ of $N$ is reachable from $x$ if and only if every $I_\nu$ contains some $i$ with $y_i=0$.
4. The trap spaces of $N$ are the subcubes $x[I]$ with $x$ a fixed point such that each $i\in\mathcal S(I)\setminus I$ has a neighbour $j\in\mathcal S(i)\setminus I$ with $x_j=0$; for every state $y$ of $F$, every fixed point in the minimal trap space containing $y$ is reachable from $y$.

## Expansion

From $\mathbf 1$, switch off one at a time the cells of the target's zero set, which is an independent set; each still has all neighbours on when its turn comes, so the update is admissible, and the remaining cells already have their target value. For item 3, a cell turns on only if some neighbour is off and turns off only if all neighbours are on. Hence the last remaining zero of a connected block of zeros, whose neighbours are all on, can never turn on, and no zero can appear next to it, so every block keeps a zero forever; conversely the target's zeros inside each block can be reached by growing and moving zeros within the block. Paths for $N$ lift to $F$ by the elimination lemma, and every state of $F$ reaches a state of the form $(n,\bar n)$ by updating Delta, which gives item 1 for $F$. So the asynchronous model reaches a minimal vertex cover from any initial condition, but which patterns are reachable depends on the initial arrangement of low-Notch cells.

## Depends on

- [Delta–Notch fixed points are minimal vertex covers](delta-notch-fixed-points-are-minimal-vertex-covers.md)

## Sources

- E. Tonello and H. Siebert, "Boolean analysis of lateral inhibition", Journal of Mathematical Biology 81(2) (2020) 463–486, <https://doi.org/10.1007/s00285-020-01515-9>, PMCID PMC7427764. Theorems 3.2–3.3 and 4.1–4.6.
