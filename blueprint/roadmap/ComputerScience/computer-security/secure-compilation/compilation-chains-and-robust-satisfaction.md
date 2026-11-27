# Compilation chains and robust satisfaction

A *compilation chain* consists of a source and a target language, each with partial programs $P$ and contexts $C$ that link into whole programs $C[P]$ and a
semantics $C[P] \rightsquigarrow t$ producing traces $t$, together with a compiler
mapping each source partial program $\mathsf P$ to a target partial program $\mathsf P{\downarrow}$; no structure is assumed on programs or contexts. Events are drawn from a nonempty set common to both languages. A *trace* is an infinite sequence of events, or a finite sequence of events ended by a
*termination event* $\varepsilon$ (visible termination, possibly recording how the program ended) or by a *divergence marker* (silent divergence). A *finite prefix*
$m$ is a finite sequence of events ended by a termination event $\varepsilon$ (a terminated prefix) or by the open-end symbol $\circ$ (a prefix that can still be extended).
The *prefix relation* is $\varepsilon \le \varepsilon$, $\circ \le t$ for every trace $t$, and $e \cdot m' \le e \cdot t'$ whenever $m' \le t'$. So a terminated prefix extends only to the completed
trace it ends, while $\circ$ cannot distinguish divergence from later events or termination. The *behaviour* of a whole program $W$ is
$\mathrm{Behav}(W) = \{t \mid W \rightsquigarrow t\}$, and $W$ *produces* a finite prefix $m$, $W \rightsquigarrow m$, if $W \rightsquigarrow t$ for some $t \ge m$.

A *trace property* is a set $\pi$ of traces; a whole program $W$ satisfies $\pi$ if $\mathrm{Behav}(W) \subseteq \pi$, and a partial program $P$ *robustly satisfies* $\pi$ if $C[P]$
satisfies $\pi$ for every context $C$ of its language, an adversarial context included. A *hyperproperty* is a set $H$ of sets of traces, satisfied by $W$ if
$\mathrm{Behav}(W) \in H$ and robustly satisfied by $P$ if $\mathrm{Behav}(C[P]) \in H$ for every context $C$.

## Sources

- C. Abate, R. Blanco, D. Garg, C. Hriţcu, M. Patrignani and J. Thibault, "Journey beyond full abstraction: exploring robust property preservation for secure compilation", *32nd IEEE Computer Security Foundations Symposium (CSF 2019)*, arXiv:1807.04603v6, <https://arxiv.org/abs/1807.04603v6>: Appendix B.1 (the event-based trace model: termination events, silent divergence, finite prefixes with $\varepsilon$ and $\circ$, and the prefix relation), Section 2.1 (compilation chains, traces and robust satisfaction of trace properties) and Section 3.1 (behaviours and hyperproperties).
