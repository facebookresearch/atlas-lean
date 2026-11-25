# Lifting free de Bruijn indices of a π-calculus name

For a cutoff $k \in \mathbb{N}$, lifting a [channel name](name.md) above $k$ leaves a free channel $c_n$ unchanged and sends a variable $\#i$ to $\#(i + 1)$ if $i \ge k$ and to $\#i$ if $i < k$. It is used to push a name under a binder.
