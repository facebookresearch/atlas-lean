# Existence of Bruhat functions

Let $G$ be a locally compact topological group and $T \le G$ a closed subgroup carrying a Haar
measure $\tau$ that is also right-invariant. For every compact $C \subseteq G$ and every
$E \subseteq TC$ there is a nonnegative, measurable, compactly supported function
$w : G \to \mathbb{R}$ with

$$\int_T w(tx)\, d\tau(t) = 1 \qquad \text{for every } x \in E.$$

## Idea

To integrate over a quotient $T \backslash G$ one wants to cut a function on $G$ down to "one copy
of each orbit" $Tx$. A Bruhat function does this softly: it is a weight whose integral along every
orbit through $E$ equals $1$. Roughly, the construction averages a compactly supported bump over $T$
and divides by the result, which also gives a continuous weight; when $G$ has a compact open
subgroup and $T$ is commutative, the weight can be chosen locally constant.

## Statements

- [Existence of a Bruhat section for a closed subgroup](exists-has-compact-support-integral-subg.md)
- [Continuous Bruhat cutoff for a closed subgroup](exists-continuous-cutoff-of-subset-mul.md): a stronger form, a continuous weight, under weaker hypotheses on $\tau$; used in the proof.
- [Continuous cutoff for a closed-embedding homomorphism](exists-continuous-cutoff-of-is-closed-em.md): the continuous form for a closed embedding of groups, used to prove it.
- [Existence of a locally constant normalized subgroup cutoff](exists-is-locally-constant-integral-subg.md): a variant: a locally constant weight when $G$ has a compact open subgroup and $T$ is commutative.
