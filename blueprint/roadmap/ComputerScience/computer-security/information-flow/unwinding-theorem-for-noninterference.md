# Unwinding theorem for noninterference

A *system* $M$ has states with an initial state $s_0$, actions $A$, outputs, a transition function $\mathrm{step}$, an output function $\mathrm{output}(s, a)$, and a domain
$\mathrm{dom}(a)$ for each action; $\mathrm{run}(s, \alpha)$ is the state reached from $s$ by the action sequence $\alpha$, so that $\mathrm{run}(s, \Lambda) = s$ for the empty sequence $\Lambda$ and
$\mathrm{run}(s, a \circ \alpha) = \mathrm{run}(\mathrm{step}(s, a), \alpha)$. A *policy* is a relation $\rightsquigarrow$ on domains; the source takes policies to be reflexive, which nothing below needs. For a domain $u$,
$\mathrm{purge}(\alpha, u)$ deletes from $\alpha$ every action $a$ with $\mathrm{dom}(a) \not\rightsquigarrow u$. $M$ is *secure* for $\rightsquigarrow$ if for every action sequence $\alpha$ and action $a$,

$$
\mathrm{output}(\mathrm{run}(s_0, \alpha), a) = \mathrm{output}(\mathrm{run}(s_0, \mathrm{purge}(\alpha, \mathrm{dom}(a))), a).
$$

That is, the output that the domain $\mathrm{dom}(a)$ observes for $a$ after $\alpha$, run from the initial state, is the same as after $\mathrm{purge}(\alpha, \mathrm{dom}(a))$.

$M$ is *view-partitioned* if each domain $u$ has an equivalence relation $\sim_u$ on states. For all states $s$, $t$, actions $a$ and domains $u$, it is
- *output consistent* if $s \sim_{\mathrm{dom}(a)} t$ implies $\mathrm{output}(s, a) = \mathrm{output}(t, a)$;
- *step consistent* if $s \sim_u t$ implies $\mathrm{step}(s, a) \sim_u \mathrm{step}(t, a)$;
- *locally respects* $\rightsquigarrow$ if $\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u \mathrm{step}(s, a)$.

**Theorem (unwinding).** Let $\rightsquigarrow$ be a relation on domains. If a view-partitioned system is output consistent, step consistent and locally respects $\rightsquigarrow$, then it is secure for $\rightsquigarrow$.

The proof shows $s \sim_u t \Rightarrow \mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{purge}(\alpha, u))$ by induction on $\alpha$: an action $a$ with $\mathrm{dom}(a) \rightsquigarrow u$ is kept by the purge and handled by step consistency, and any other action by local respect, with the symmetry and transitivity of $\sim_u$. Taking $s = t = s_0$ and $u = \mathrm{dom}(a)$, output consistency then gives security. The purge-based notion of security is intended for
transitive policies; for intransitive (channel-control) policies the purge is replaced by an intransitive purge, with a different unwinding
theorem.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 2 (Definitions 1–4, Lemma 1 and Theorem 1 with its proof) and Chapter 4 (Theorem 7, the unwinding theorem for intransitive policies).
