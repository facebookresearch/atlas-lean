# Leading zero bits leave the final CRC register polynomial unchanged

For every register width $r \in \mathbb{N}$, every width-$r$ taps word $g$, and every finite MSB-first payload $B$, prepending a $0$ bit to $B$ yields the same final register polynomial over $\mathbb{F}_2$:

$$P_{\mathrm{final}_{r, g}(0 \mathbin{::} B)} = P_{\mathrm{final}_{r, g}(B)}.$$
