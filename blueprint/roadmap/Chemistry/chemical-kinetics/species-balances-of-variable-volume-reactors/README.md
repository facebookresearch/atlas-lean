# Species balances of variable-volume reactors

The amount of species $i$ in a reactor of volume $V(t)$ is $n_i = V c_i$, where $c_i$ is its
concentration. At an instant $t$ where $V$ and $c_i$ have derivatives, the species balance
$n_i' = F_{\mathrm{in}} - F_{\mathrm{out}} + G$ (inflow, outflow and net generation rates) is
equivalent to $V' c_i + V c_i' = F_{\mathrm{in}} - F_{\mathrm{out}} + G$, and at an instant of
nonzero volume it determines $c_i'$. All statements concern a single instant.

- [Product rule for the amount $V c_i$ of a species at one instant](stock-deriv-eq.md)
- [The amount balance at an instant holds iff its concentration form does](stock-iff-concentration.md)
- [At nonzero volume, the balance gives the concentration derivative](concentration-deriv-eq-of-stock.md)
- [At constant volume $V_0$ with no flows, the balance is $V_0 c_i' = G$](closed-constant-volume.md)
