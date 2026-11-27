# Complexity of reachability and attractors in most permissive Boolean networks

**Setting.** Let $f : \mathbb{B}^n \to \mathbb{B}^n$ be a Boolean network with the most permissive (MP) semantics. $f$ is **locally monotonic** if each $f_i$ is monotone in each of its arguments (no regulator acts both as activator and inhibitor of the same target). A **trap space** of $f$ is a subcube $h \subseteq \mathbb{B}^n$ (some coordinates fixed, others free) closed under $f$, i.e. $f(z) \in h$ for all $z \in h$; it is **minimal** if it contains no other trap space. An attractor is a minimal non-empty set of configurations closed under the transition relation.

**Statements.**

1. *Transition test.* Deciding whether an MP transition of component $i$ is enabled ("$\exists z \in \gamma(x): f_i(z) = 1$") is NP-complete in general (it is SAT), and takes linear time if $f$ is locally monotonic: set dynamic activators to $1$ and dynamic inhibitors to $0$ (and conversely for $f_i(z) = 0$).
2. *Short witnesses.* If an MP trajectory exists between two configurations, one exists visiting at most $3n$ configurations, organized in three phases: Boolean states to dynamic states, switches between $\nearrow$ and $\searrow$, dynamic states to Boolean states, each component moving at most once per phase.
3. *Reachability.* Reachability between two Boolean configurations is decidable in polynomial time for locally monotonic $f$ (exploring at most quadratically many transitions, and $O(n)$ when the target lies in an attractor), and is in $\mathrm{P}^{\mathrm{NP}}$ in general. For synchronous and asynchronous Boolean networks it is PSPACE-complete.
4. *Attractors.* The attractors of the MPBN are exactly the minimal trap spaces of $f$. Deciding whether a configuration belongs to an attractor is in coNP for locally monotonic $f$ and in $\mathrm{coNP}^{\mathrm{coNP}}$ in general, versus PSPACE-complete for synchronous and asynchronous semantics. Deciding whether some attractor configuration is reachable from a given configuration has the same complexity as the attractor problem.

## Expansion

For item 1, in a locally monotonic network the extreme interpretation (all dynamic activators on, all dynamic inhibitors off) maximizes $f_i$ over $\gamma(x)$, so one evaluation decides the existence question. For item 3 the reachability algorithm greedily applies as many phase-one transitions as possible; components whose value must end where it started but cannot return are forbidden from leaving their Boolean state and the exploration restarts, at most $n$ times; the final phase then settles all dynamic components. For item 4, whenever two configurations on a diagonal of a subcube are mutually reachable under MP dynamics, so are the adjacent vertices, so closed sets of configurations are unions of subcubes and the minimal closed sets are minimal trap spaces; membership reduces to checking minimality of the smallest trap space containing the configuration. Minimal trap spaces can be enumerated with SAT or answer-set solvers, and in published models of bladder tumorigenesis and T-cell differentiation they matched the asynchronous attractors; reachable attractors of random scale-free networks with $10^5$ components were computed in under a minute.

## Depends on

- [Most permissive semantics of Boolean networks and completeness for refinements](most-permissive-semantics-and-completeness-for-refinements.md)

## Sources

- L. Paulevé, J. Kolčák, T. Chatain, S. Haar, "Reconciling qualitative, abstract, and scalable modeling of biological networks", Nature Communications 11 (2020), 4256, Results ("Simpler computational complexity") and Supplementary Notes 1–2 (Theorems 3–4), <https://doi.org/10.1038/s41467-020-18112-5> (PMC7450094).
- H. Klarner, A. Bockmayr, H. Siebert, "Computing maximal and minimal trap spaces of Boolean networks", Natural Computing 14 (2015), 535–544, <https://doi.org/10.1007/s11047-015-9520-7>.
