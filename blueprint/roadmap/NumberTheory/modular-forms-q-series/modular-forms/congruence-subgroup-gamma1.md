# Congruence subgroup $\Gamma_1(N)$

For a natural number $N$, $\Gamma_1(N)$ is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of the matrices
$\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ with $a \equiv d \equiv 1 \pmod N$ and $c \equiv 0 \pmod N$,
that is, whose bottom row is congruent to $(0, 1)$ modulo $N$. It is contained in
[$\Gamma_0(N)$](congruence-subgroup-gamma0.md).

In Mathlib this is [`CongruenceSubgroup.Gamma1`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L131 "CongruenceSubgroup.Gamma1"), defined as
the image in $\mathrm{SL}_2(\mathbb{Z})$ of the kernel of the reduction map $\Gamma_0(N) \to \mathbb{Z}/N\mathbb{Z}$,
$\gamma \mapsto d \bmod N$; `CongruenceSubgroup.Gamma1_mem` describes its elements as above.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §0, p. 523 (the definition of
  $\Gamma_1(N)$).
