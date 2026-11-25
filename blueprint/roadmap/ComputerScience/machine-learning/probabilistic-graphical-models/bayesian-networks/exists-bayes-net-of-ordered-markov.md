# Markov laws factorize

**Markov laws factorize** ((O) ⇒ (F); Lauritzen 2009): let $\alpha$ be a finite nonempty type
and $P : \alpha^n \to \mathbb{R}$ a probability distribution. If $P$ has the ordered Markov
property for parent sets $\mathrm{pa}(k) \subseteq \{0, \dots, k-1\}$, then $P$ is the joint
distribution of a Bayesian network with these parent sets, namely the network of its
conditional laws given the parents. No positivity is assumed.

The proof shows by induction along the order that the law of the first $m$ variables is the
product of the conditional tables of the first $m$ nodes: the ordered Markov property at node $m$
turns $P(x_{<m+1})$ into $P(x_{<m}) \, P(x_m \mid x_{\mathrm{pa}(m)})$, and when
$P(x_{\mathrm{pa}(m)}) = 0$ both sides vanish. This is where no positivity assumption is needed,
in contrast with the Hammersley–Clifford theorem for undirected graphs.

## Background

- [The ordered Markov property](cond-eq-cpt.md): the same property, in ratio form, for the joint
  of a given network.
- [The local directed Markov property](cond-indep-local.md): the stronger property (L) that every
  factorizing law has; it gives the converse direction,
  [factorizing laws have the ordered Markov property](ordered-markov-joint.md).
