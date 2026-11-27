# Certificate checks give weak bisimilarity

Let $f$ realize the code-level transition
function $s$ and $g$ realize $t$ for a recursive specification, and let $R$ be a list of code
pairs on which the certificate check of $s$, $t$ and $R$ succeeds. Then for every pair $(x, y)$
in $R$, the processes $f(x)$ and $g(y)$ are weakly bisimilar in the labelled transition system
of the specification.
