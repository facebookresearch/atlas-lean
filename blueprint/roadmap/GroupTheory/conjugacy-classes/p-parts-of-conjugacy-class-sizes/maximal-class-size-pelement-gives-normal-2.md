# A maximal p-part of a class size does not force a normal p-complement

For a prime $p$, the
$p$-part of a positive integer $m$ is the largest power of $p$ dividing $m$. There exist a finite
group $G$, a prime $p$ and a $p$-element $g$ of $G$ (that is, $g^{p^k} = 1$ for some natural
number $k$) such that for every $x \in G$ the $p$-part of the size of the conjugacy class of $x$
is at most the $p$-part of the size of the conjugacy class of $g$, but $G$ has no normal
$p$-complement.

Sambale's counterexample is the group $\mathrm{SL}(2, 3) \rtimes Q_8$ of order $192$ (number $945$
in the GAP library of small groups) with $p = 2$. In it an element of order $4$ has class size
$24$, whose $2$-part $8$ is the largest $2$-part of a class size, while the eight elements of
order $3$ form one conjugacy class, so there is no normal subgroup of order $3$, that is, no
normal $2$-complement.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.27 (I. B. Gorshkov); resolution: B. Sambale, letter of 16 February 2022, recorded in the Kourovka Notebook (21st issue), Problem 20.27: "No, not necessarily, a counterexample is given by SmallGroup(192,945)", https://arxiv.org/abs/1401.0300v49.
