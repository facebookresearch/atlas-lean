# Total while preconditions are least fixed points

For every IMP guard $b$, body $c$ and assertion $Q$, $\{s:\operatorname{wp}(\mathrm{while}\ b\ c,Q)(s)\}$ is the least fixed point, under inclusion, of $F(I)=\{s:(b(s)=\mathrm{false}\land Q(s))\lor(b(s)=\mathrm{true}\land\operatorname{wp}(c,\mathbf1_I)(s))\}$. Divergent starting states are excluded; no uniform bound on the number of iterations is imposed.
