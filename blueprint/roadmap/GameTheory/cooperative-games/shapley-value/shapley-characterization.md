# Existence and uniqueness of the Shapley value

On a fixed finite set $N$ of players, there is exactly one linear map $\varphi$ from TU games on
$N$ to payoff vectors in $\mathbb R^N$ that is

- efficient: $\sum_{i \in N} \varphi_i(v) = v(N)$;
- symmetric: if a permutation $\sigma$ of $N$ leaves $v$ invariant, then $\varphi_{\sigma i}(v) = \varphi_i(v)$;
- null for null players: if $v(S \cup \{i\}) = v(S)$ for every coalition $S$ not containing $i$, then $\varphi_i(v) = 0$.

The proof writes $v$ in the basis of unanimity games $u_T(S) = [T \subseteq S]$ by Möbius
inversion, $v = \sum_{T \neq \emptyset} c_T(v)\, u_T$, and shows that the axioms force
$\varphi_i(u_T) = 1/|T|$ for $i \in T$ and $0$ otherwise; hence
$\varphi_i(v) = \sum_{T \ni i} c_T(v)/|T|$.

Compared with the source: Shapley works with superadditive games on a universe of players with
finite carriers and an additivity axiom; this is an adapted characterisation on a fixed finite
player set, with linearity in place of additivity and the null-player axiom made explicit.

## Background

- [Efficient value](is-efficient.md), [Symmetric value](is-symmetric.md) and
  [Null player axiom](satisfies-null-player-axiom.md): the three axioms.
- [Bondareva–Shapley theorem](../bondareva-shapley-theorem/README.md): the core, the other
  classical solution concept for TU games.

## Related topics

- [The Shapley value is given by Shapley's formula](eq-shapley-formula.md): the classical
  formula, an average of marginal contributions, derived from this uniqueness.

## Sources

- L. S. Shapley, "A value for n-person games", in Contributions to the Theory of Games II, Ann. of Math. Stud. 28, Princeton Univ. Press (1953), 307–317 (cited as in the secondary sources below; not consulted for this page).
- Encyclopedia of Mathematics, "Shapley value" (secondary source: the axioms of efficiency, symmetry and linearity), https://encyclopediaofmath.org/wiki/Shapley_value.
