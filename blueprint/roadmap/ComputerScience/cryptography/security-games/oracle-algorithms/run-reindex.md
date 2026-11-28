# Running a translated algorithm

Let $c$ be an adaptive oracle algorithm with queries in
$X$ and answers in $Y$, let $f : X \to P$ and $g : X \to Z \to Y$, and let $O : P \to Z$. Running
the algorithm obtained from $c$ by translating its queries along $f$ and its answers along $g$
against $O$ gives the output of $c$ run against the oracle $x \mapsto g(x, O(f(x)))$.
