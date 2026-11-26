# Interventional law of a binary structural causal model

For a binary structural causal model on $X \to Y$ with noise in a finite type $U$ and weights $p_U$, an intervention $i$ and values $x, y \in \{0,1\}$, the weight of the event $X = x,\ Y = y$ in regime $i$ is

$$P_i(X = x, Y = y) = \sum_{u \in U :\ X_i(u) = x,\ Y_i(u) = y} p_U(u),$$

where $X_i(u)$ and $Y_i(u)$ are the values of $X$ and $Y$ under $i$ at noise $u$. When the weights form a probability mass function this is the joint law of $(X, Y)$ under the intervention.
