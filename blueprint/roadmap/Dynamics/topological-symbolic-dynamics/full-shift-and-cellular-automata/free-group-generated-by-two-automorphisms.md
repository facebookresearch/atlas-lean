# Whether two automorphisms of a full shift generate a free group of rank two is undecidable

For a suitable finite alphabet, no algorithm decides, given two reversible cellular automata on the full shift (automorphisms given by local rules), whether they generate a free group of rank two.

Let $S$ be a finite alphabet and $\mathrm{Aut}(S^{\mathbb{Z}})$ the automorphism group of the full shift $S^{\mathbb{Z}}$: the homeomorphisms of $S^{\mathbb{Z}}$ commuting with the shift, that is, the reversible cellular automata. An automorphism is given to an algorithm by a local rule $F\colon S^{2r+1} \to S$, with $f(x)_i = F(x_{[i-r, i+r]})$; whether two local rules define the same cellular automaton is decidable.

**Theorem.** Given $f, g \in \mathrm{Aut}(S^{\mathbb{Z}})$, it is undecidable whether the subgroup $\langle f, g \rangle$ is isomorphic to the free group $F_2$ (Theorem 6 of the source). Here $S$ is an alphabet for which the torsion problem of $\mathrm{Aut}(S^{\mathbb{Z}})$, deciding whether a given automorphism has finite order, is undecidable; such an alphabet exists (Theorem 3 of the source).

## Depends on

- [Automorphism group of the full shift](automorphism-group.md)
- [Full shift space](full-shift-space.md)
- [One-dimensional cellular automaton](is-one-dimensional-ca.md)

## Proof depends on

None.

## Expansion

The main theorem of the source says that, for $|S| \ge 2$, the class of groups isomorphic to subgroups of $\mathrm{Aut}(S^{\mathbb{Z}})$ is closed under free products (Theorem 2). Its proof places the actions of the factors on disjoint "conveyor belts" of the configuration, delimited by unbordered marker words, and adds an alphabet component through which the ends of neighboring belts communicate, so that alternating products of elements of the factors act as in the free product. The source obtains the theorem by combining this closure property with the undecidability of the torsion problem of $\mathrm{Aut}(S^{\mathbb{Z}})$ for some alphabet $S$, a result of Kari that it quotes as Theorem 3; it states the reduction without detailed proof.

## Sources

- V. Salo, "A note on subgroups of automorphism groups of full shifts", Ergodic Theory and Dynamical Systems 38 (2018), no. 4, 1588–1600, https://doi.org/10.1017/etds.2016.95; read in arXiv:1507.00820v1 (Theorems 2, 3 and 6 and the decidability lemma for local rules in the section "Decidability" of arXiv:1507.00820v1).
