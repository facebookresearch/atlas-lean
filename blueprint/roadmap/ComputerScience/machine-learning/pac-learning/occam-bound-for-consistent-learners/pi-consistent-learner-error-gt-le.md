# Consistent learners over a finite class are probably approximately correct

Let $H$ be a finite set of hypotheses with measurable disagreement sets, $D$ a probability
distribution under which some $h \in H$ has error $0$, and $A$ a learner on samples of size $m$
that is consistent with $H$ (on every sample realizable by $H$,
its output lies in the version space). Then for every $\varepsilon \in [0, \infty]$, with $(1 - \varepsilon)_+ = \max(1 - \varepsilon, 0)$ and $0^0 = 1$,

$$D^m\{S : \operatorname{error}_D(A(S)) > \varepsilon\} \le |H|\,(1 - \varepsilon)_+^m ,$$

where $D^m$ of the event is its outer measure: the learner is an arbitrary map, so the event need
not be measurable.

The learner is only required to be consistent on realizable samples; the samples on which it is
unconstrained have probability $0$ by the previous statement.

## Sources

- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, *Occam's razor*, Information Processing Letters 24 (1987), 377-380.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Section 2.3.1.
