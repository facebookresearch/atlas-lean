# Value of the effect under an intervention

In a binary structural causal model on $X \to Y$ with structural equation $Y = f_Y(X, u)$, the value of $Y$ under an intervention $(i_X, i_Y)$ at noise $u$ is $y$ if $i_Y$ sets $Y := y$, and otherwise $f_Y(X_i(u), u)$, where $X_i(u)$ is the value of $X$ under the same intervention at $u$.
