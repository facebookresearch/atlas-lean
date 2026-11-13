# The Freund–Schapire bound on AdaBoost's training error

Let AdaBoost run on $m > 0$
training points with labels $y$ and a weak learner with edge $\gamma \ge 0$, that is, one that on
every weighting $D$ of the training points with $D_i > 0$ for all $i$ and $\sum_i D_i = 1$ returns
a hypothesis whose weighted error under $D$ lies in $(0, 1/2 - \gamma]$. Write $\varepsilon_t$ for
the weighted error of the weak hypothesis of round $t$ under AdaBoost's weights of that round.
Then for every number of rounds $T$, the training error after $T$ rounds is at most
$\prod_{t < T} 2\sqrt{\varepsilon_t (1 - \varepsilon_t)}$.
