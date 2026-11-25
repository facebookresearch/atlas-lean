# Adding a completed role preserves the guard condition

Let $\Delta$ be an ownership context, $e$, $z$ endpoints, $k$ a natural number and $c$ a capability
whose protocol has head $\mathrm{end}$. If $\mathrm{Min}_\Delta(e,k)$ holds (every endpoint $d \ne
e$ with an active capability in $\Delta$ has rank $> k$), then $\mathrm{Min}_{\Delta[z \mapsto
c]}(e,k)$ holds, where $\Delta[z \mapsto c]$ maps $z$ to $c$ and agrees with $\Delta$ elsewhere.
