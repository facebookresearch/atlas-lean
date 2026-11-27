# The isomorphism problem for finitely presented subgroups of some right-angled Artin group is unsolvable

There is a right-angled Artin group $A$ such that no algorithm decides whether two finitely presented subgroups of $A$, each given by a finite generating set and a finite presentation, are isomorphic.

A right-angled Artin group is a group with a presentation $\langle v_1, \dots, v_n \mid [v_i, v_j] = 1 \ ((i, j) \in E) \rangle$ for a set $E$ of pairs. There exists a right-angled Artin group $A$ such that the isomorphism problem for the finitely presented subgroups of $A$ is unsolvable (Theorem 1.1 of the source).

The corresponding statement for finitely generated subgroups is much easier; the point is that the subgroups are finitely presented. Since every right-angled Artin group embeds in the mapping class group of every closed surface of sufficiently high genus, the same holds there.

## Depends on

- [Group](../../../group-basics/group.md)
- [Artin group](../artin-groups/artin-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Bridson and Miller proved (Theorem 4.1 of the source): if $1 \to N \to \Gamma \to L \to 1$ is exact with $\Gamma$ torsion-free hyperbolic, $N$ infinite and finitely generated, and $L$ non-abelian free, then the isomorphism problem for finitely presented subgroups of $\Gamma \times \Gamma \times F$, with $F$ non-abelian free, is unsolvable; in more detail, there is a recursive sequence of finite subsets $\Delta_i$ of $\Gamma \times \Gamma \times F$, with finite presentations $\langle \Delta_i \mid \Theta_i \rangle$ of the subgroups they generate, such that no algorithm decides whether $\langle \Delta_i \mid \Theta_i \rangle \cong \langle \Delta_0 \mid \Theta_0 \rangle$. The Haglund–Wise version of the Rips construction, applied to a finitely generated non-abelian free group $Q$, gives $1 \to N \to \Gamma \to Q \to 1$ with $N$ finitely generated and $\Gamma$ hyperbolic and virtually special. A finite-index subgroup $\Gamma_0$ embeds in a right-angled Artin group $A$, and with $N_0 = N \cap \Gamma_0$ and $Q_0$ the image of $\Gamma_0$ (again non-abelian free) the criterion applies to $\Gamma_0 \times \Gamma_0 \times F$, a subgroup of the right-angled Artin group $A \times A \times F$.

## Sources

- M. R. Bridson, "On the subgroups of right-angled Artin groups and mapping class groups", Mathematical Research Letters 20 (2013), no. 2, 203–212, https://doi.org/10.4310/MRL.2013.v20.n2.a1; read in arXiv:1205.5416v1 (Theorem 1.1 and Theorem 4.1 of arXiv:1205.5416v1).
