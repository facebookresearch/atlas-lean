# Training error of AdaBoost

Let AdaBoost run on $m$ training points with labels $y$,
read labels and predictions as $\pm 1$, and let $F_T$ be the combined score after $T$ rounds.
The training error after $T$ rounds is the number of training points $i$ with
$y_i F_T(i) \le 0$, divided by $m$; in particular a zero score counts as an error.
