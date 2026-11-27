# Sample complexity of a finite class

Let $H$ be a finite set of hypotheses with measurable disagreement sets, $D$ a probability
distribution satisfying the realizability assumption (some $h \in H$ has error $0$), $A$ a learner
consistent with $H$, and $\varepsilon > 0$, $\delta > 0$ and

$$m \ge \frac{\log(|H| / \delta)}{\varepsilon}.$$

Then $D^m\{S : \operatorname{error}_D(A(S)) > \varepsilon\} \le \delta$, an outer-measure bound since the learner
is an arbitrary map: with probability at least $1 - \delta$ over $m$ independent examples, the learner's hypothesis has error at most
$\varepsilon$. Consistent learners are the empirical risk minimizers of the realizable case, so this
is the textbook corollary for ERM rules over a finite class, stated for consistent learners.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Corollary 2.3.
- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, *Occam's razor*, Information Processing Letters 24 (1987), 377-380.
