# Robust sunflowers contain sunflowers

If $\mathcal{F}$ is a $(1/r, 1/r)$-robust sunflower with kernel $K$, then $\mathcal{F}$ contains $r$ sets $F_1, \dots, F_r$ whose petals $F_i \setminus K$ are pairwise disjoint, i.e. an $r$-sunflower.

## Proof sketch

Colour each element of $X \setminus K$ independently and uniformly with one of $r$ colours; each colour class $W_i$ is a $1/r$-random subset, so it fails to contain a petal with probability strictly less than $1/r$. By the union bound, with positive probability every colour class contains some petal $F_i \setminus K$; these petals lie in disjoint colour classes, hence are pairwise disjoint, and $F_1, \dots, F_r$ form an $r$-sunflower.

## Depends on

- [Robust sunflowers](robust-sunflowers-and-satisfying-systems.md)

## Sources

- Ryan Alweiss, Shachar Lovett, Kewen Wu, Jiapeng Zhang, "Improved bounds for the sunflower lemma", Annals of Mathematics 194(3) (2021), STOC (2020); arXiv:1908.08483.
- Anup Rao, "Coding for sunflowers", Discrete Analysis 2020:2 (2020); arXiv:1909.04774.
