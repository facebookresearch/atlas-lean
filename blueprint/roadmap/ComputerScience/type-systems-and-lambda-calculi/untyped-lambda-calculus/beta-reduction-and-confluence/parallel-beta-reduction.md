# Parallel β-reduction

*Parallel β-reduction* $\Rightarrow$ on untyped λ-terms is the least relation closed under the rules

- $P \Rightarrow P$;
- if $P \Rightarrow P'$ then $\lambda x.\, P \Rightarrow \lambda x.\, P'$;
- if $P \Rightarrow P'$ and $Q \Rightarrow Q'$ then $P\, Q \Rightarrow P'\, Q'$;
- if $P \Rightarrow P'$ and $Q \Rightarrow Q'$ then $(\lambda x.\, P)\, Q \Rightarrow P'[x := Q']$.

Intuitively $P \Rightarrow P'$ contracts any set of redexes already present in $P$ simultaneously, but no redex created by these contractions: for example
$(\lambda x.\, x\, x)(\lambda x.\, x) \Rightarrow (\lambda x.\, x)(\lambda x.\, x)$ but not $\Rightarrow \lambda x.\, x$. One-step reduction is contained in it, and it is contained in
multi-step reduction: ${\to_\beta} \cup {=} \subseteq {\Rightarrow} \subseteq {\twoheadrightarrow_\beta}$, so $\twoheadrightarrow_\beta$ is the transitive closure of $\Rightarrow$.

## Depends on

- [β-reduction](beta-reduction.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 1.4.3 and Lemma 1.4.6.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, the relation ρ defined by rules 1–4 in the proof of Theorem 1.24, Lemma 1.26 and the remark after the proof.
