# Unwinding theorem for noninterference

A *system* $M$ has states with an initial state, actions $A$, outputs, a transition function $\mathrm{step}$, an output function $\mathrm{output}(s, a)$, and a domain
$\mathrm{dom}(a)$ for each action; $\mathrm{run}(s, \alpha)$ is the state reached by the action sequence $\alpha$. A *policy* is a reflexive relation $\rightsquigarrow$ on domains. For a domain $u$,
$\mathrm{purge}(\alpha, u)$ deletes from $\alpha$ every action $a$ with $\mathrm{dom}(a) \not\rightsquigarrow u$. $M$ is *secure* for $\rightsquigarrow$ if for every domain $u$, action $a$ with $\mathrm{dom}(a) = u$ and
sequence $\alpha$, the output to $u$ after $\alpha$ equals that after $\mathrm{purge}(\alpha, u)$.

$M$ is *view-partitioned* if each domain $u$ has an equivalence relation $\sim_u$ on states. It is
- *output consistent* if $s \sim_{\mathrm{dom}(a)} t$ implies $\mathrm{output}(s, a) = \mathrm{output}(t, a)$;
- *step consistent* if $s \sim_u t$ implies $\mathrm{step}(s, a) \sim_u \mathrm{step}(t, a)$;
- *locally respects* $\rightsquigarrow$ if $\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u \mathrm{step}(s, a)$.

**Theorem (unwinding).** If a view-partitioned system is output consistent, step consistent and locally respects $\rightsquigarrow$, then it is secure for $\rightsquigarrow$.

The proof shows $s \sim_u t \Rightarrow \mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{purge}(\alpha, u))$ by induction on $\alpha$. The purge-based notion of security is intended for
transitive policies; for intransitive (channel-control) policies the purge is replaced by an intransitive purge, with a different unwinding
theorem.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Section 2 (Definitions 1–4, Lemma 1 and Theorem 1 with its proof) and Section 4 (Theorem 7, the unwinding theorem for intransitive policies).
