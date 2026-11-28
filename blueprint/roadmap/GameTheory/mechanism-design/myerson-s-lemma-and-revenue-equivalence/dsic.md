# Dominant-strategy incentive compatibility of a single-parameter auction

An auction for $n$ bidders with allocation rule $x$ and payment rule $\mathrm{pay}$, both maps from bid profiles $b \in \mathbb{R}^n$ to $\mathbb{R}^n$, is dominant-strategy incentive compatible when, for every bidder $i$, every valuation $v_i \ge 0$, every report $b_i \ge 0$ and every profile $b_{-i}$ of nonnegative bids,

$$v_i\, x_i(b_i, b_{-i}) - \mathrm{pay}_i(b_i, b_{-i}) \le v_i\, x_i(v_i, b_{-i}) - \mathrm{pay}_i(v_i, b_{-i}),$$

where $(z, b_{-i})$ is the profile $b_{-i}$ with bidder $i$'s entry replaced by $z$. Values of $x$ and $\mathrm{pay}$ at profiles with a negative entry play no role.
