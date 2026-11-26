# Congruence subgroup $\Gamma_0(N)$

For a natural number $N$, $\Gamma_0(N)$ is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of the matrices
$\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ with $c \equiv 0 \pmod N$.

In Mathlib this is [`CongruenceSubgroup.Gamma0`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L78 "CongruenceSubgroup.Gamma0"): the matrices
`g` with `(g 1 0 : ZMod N) = 0`.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §0, p. 523 (the definition of
  $\Gamma_0(N)$).
