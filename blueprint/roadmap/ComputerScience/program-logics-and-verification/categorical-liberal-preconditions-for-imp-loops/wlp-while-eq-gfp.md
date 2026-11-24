# While liberal preconditions are greatest fixed points

For any guard $b$, body $c$ and assertion $Q$, the state set satisfying $\operatorname{wlp}(\mathrm{while}\ b\ c,Q)$ is the greatest fixed point of $F(I)=\{s:(b(s)=\mathrm{false}\Rightarrow Q(s))\land(b(s)=\mathrm{true}\Rightarrow\operatorname{wlp}(c,\mathbf1_I)(s))\}$. Sets are ordered by inclusion.
