# Möbius function of the poset of finite subsets

In the poset of finite subsets of a set, ordered by inclusion, the Möbius function is

$$\mu(S, T) = (-1)^{|T \setminus S|} \qquad (S \subseteq T).$$

Each interval $[S, T]$ is isomorphic to the Boolean lattice of subsets of $T \setminus S$, of length
$|T \setminus S|$, so this says $\mu(S, T) = (-1)^{\ell(S, T)}$. With it, Möbius inversion on a
Boolean algebra is the principle of inclusion-exclusion.

Stanley derives the formula from the product theorem; it also follows by induction on $T$ from
$\sum_{S \subseteq U \subseteq T} (-1)^{|U \setminus S|} = 0$ for $S \ne T$.

## Informally uses

- [Product theorem for the Möbius function](mu-prod-apply.md): Stanley writes $B_n \cong 2^n$ and
  multiplies the Möbius function of the two-element chain over the $n$ factors.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Example 3.8.3, for the Boolean algebra $B_n$ of subsets of an $n$-element set.
