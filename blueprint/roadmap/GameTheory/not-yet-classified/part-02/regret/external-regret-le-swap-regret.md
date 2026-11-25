# External regret is at most swap regret

Let $x_t$ be mixed strategies (probability vectors) over a finite nonempty action set at times $t = 1, \dots, T$, and let $\ell_t$ be loss vectors. With expected loss $\sum_t\sum_a x_t(a)\ell_t(a)$, external regret is the expected loss minus $\min_{a}\sum_t \ell_t(a)$, and swap regret is the expected loss minus $\min_{\delta}\sum_t\sum_a x_t(a)\ell_t(\delta(a))$ over all maps $\delta$ of actions. Then external regret is at most swap regret.
