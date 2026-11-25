# Sequential Glosten–Milgrom model: quotes as conditional expectations

An asset has value $V \in \{V_L, V_H\}$ with $V_L < V_H$ and prior $\theta_0 = \mathbb P(V = V_H) \in (0, 1)$. In each period $t = 1, 2, \dots$ one trader arrives. The trader types are drawn independently across periods and independently of $V$: in each period the trader is informed with probability $\mu \in [0, 1)$ and uninformed otherwise. An informed trader buys if $V = V_H$ and sells if $V = V_L$; an uninformed trader buys or sells with probability $1/2$ each, independently of $V$, of all trader types and of the orders in other periods. A competitive risk-neutral market maker posts, given the history $\mathcal H_{t-1}$ of past trades,

$$a_t = \mathbb E[V \mid \mathcal H_{t-1}, \text{buy at } t], \qquad b_t = \mathbb E[V \mid \mathcal H_{t-1}, \text{sell at } t].$$

Given $V$, the trade directions are independent across periods, with buy probability $\mu + (1-\mu)/2$ if $V = V_H$ and $(1-\mu)/2$ if $V = V_L$. If $\theta = \mathbb P(V = V_H \mid \mathcal H_{t-1})$, Bayes' rule gives

$$\mathbb P(V = V_H \mid \mathcal H_{t-1}, \text{buy}) = \frac{\theta\, (1 + \mu)}{\theta\, (1 + \mu) + (1 - \theta)(1 - \mu)}, \qquad \mathbb P(V = V_H \mid \mathcal H_{t-1}, \text{sell}) = \frac{\theta\, (1 - \mu)}{\theta\, (1 - \mu) + (1 - \theta)(1 + \mu)},$$

and $b_t \le \mathbb E[V \mid \mathcal H_{t-1}] \le a_t$, with strict inequalities when $\mu > 0$. The sequence $\mathbb E[V \mid \mathcal H_t]$ of transaction prices is a martingale with respect to the history.

## Sources

- L. R. Glosten and P. R. Milgrom, "Bid, ask and transaction prices in a specialist market with heterogeneously informed traders", *Journal of Financial Economics* 14(1):71–100, 1985
