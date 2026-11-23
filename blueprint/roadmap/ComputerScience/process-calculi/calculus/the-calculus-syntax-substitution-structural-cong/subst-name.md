# Substitution of a name into a π-calculus name

Let $n$ be a [channel name](name.md) and $k \in \mathbb{N}$ a cutoff. Substituting $n$ for the variable $\#k$ in a name leaves a free channel $c_m$ unchanged and sends a variable $\#i$ to $\#i$ if $i < k$ (bound by an inner binder), to $n$ if $i = k$, and to $\#(i - 1)$ if $i > k$ (the binder of $\#k$ disappears).
