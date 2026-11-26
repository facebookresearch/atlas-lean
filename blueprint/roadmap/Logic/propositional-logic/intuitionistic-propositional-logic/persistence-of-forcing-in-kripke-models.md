# Persistence of forcing in Kripke models

In every [Kripke model](kripke-models-for-ipc.md) $(C, \le, \Vdash)$, if $c \le c'$ and $c \Vdash \varphi$, then $c' \Vdash \varphi$, for every formula $\varphi$.

**Proof.** By induction on $\varphi$: atoms by the persistence condition, $\bot$ trivially, $\wedge$ and $\vee$ from the induction hypothesis, and $\to$ by transitivity of $\le$, since every state above $c'$ is above $c$.

## Depends on

- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: the generalized monotonicity after Definition 2.5.2, proved by induction.
