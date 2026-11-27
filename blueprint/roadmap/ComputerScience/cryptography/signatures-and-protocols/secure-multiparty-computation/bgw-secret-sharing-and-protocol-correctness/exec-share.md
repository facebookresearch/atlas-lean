# Share-level execution of a BGW program

Let $F$ be a field and $\mathrm{Party}$ a finite type of parties, with Shamir parameters giving a threshold $t$ and an evaluation point $\alpha_i \in F$ for each party $i$, and let $\lambda : \mathrm{Party} \to F$ be arbitrary weights (the definition assumes no recombination property of $\lambda$). Fix a straight-line program over addition and multiplication gates with $\mathrm{inputCount}$ inputs and $\mathrm{gateCount}$ gates, inputs $x \in F^{\mathrm{inputCount}}$, input tapes $\mathrm{tapeIn}(k) \in F^t$ and per-gate tapes $\mathrm{tapeMul}(g) : \mathrm{Party} \to F^t$. Share-level execution assigns to every wire a share function $\mathrm{Party} \to F$:

- an **input wire** $k$ gets the [input shares](input-shares.md) of $x_k$: party $j$ holds its Shamir share of $x_k$ under $\mathrm{tapeIn}(k)$;
- a **gate wire** $g$ gets the [gate share function](gate-shares.md) of $g$, computed from those input shares with the weights $\lambda$ and $\mathrm{tapeMul}$.
