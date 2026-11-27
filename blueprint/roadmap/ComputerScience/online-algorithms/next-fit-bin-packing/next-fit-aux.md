# Next Fit from a given state

Next Fit bin packing with unit bins, from a given state: given item sizes $x_1, \dots, x_m$, a number $b$ of bins already started and the current load $\ell$, Next Fit adds the next item $x$ to the current bin if $\ell + x \le 1$, and otherwise starts a new bin with load $x$ ($b \leftarrow b + 1$); the value is the final $b$.
