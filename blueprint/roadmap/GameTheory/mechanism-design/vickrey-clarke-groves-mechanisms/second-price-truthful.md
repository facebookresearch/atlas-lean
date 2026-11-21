# Vickrey's theorem

Let $I$ be a finite set of at least two agents, and let $w$ be a winner rule that picks a highest bid:
$t_j \le t_{w(t)}$ for every bid vector $t$ and every agent $j$. Let $t$ be a vector of nonnegative bids,
$i$ an agent and $s \ge 0$, and let $t'$ be $t$ with $t_i$ replaced by $s$. With value $t_i$, the utility of
agent $i$ at bids $u$ is $t_i - \pi_i(u)$ if $w(u) = i$ and $-\pi_i(u)$ otherwise, where $\pi_i(u)$ is the
second-price payment. Bidding $s$ instead of its value does not help agent $i$: its utility at $t'$ is at
most its utility at $t$ (Vickrey 1961, through Nisan 2007, Proposition 9.13). The statement is for
nonnegative values and bids, the valuation domain of Nisan 2007, §9.3.5.1, and is derived from the VCG
theorem.

## Informally uses

- [VCG truthfulness, pointwise](groves-payment-truthful.md): applied to single-item valuations, where the highest bid maximizes the welfare.
- [The second-price auction is the VCG mechanism with Clarke pivot payments](groves-payment-single-item.md): to identify the payments.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Definition 9.12 and Proposition 9.13 (crediting Vickrey 1961), and §9.3.5.1; Proposition 9.13 there is stated for all real bids, and the statement here is restricted to nonnegative bids.
