# Latent projection

For a Bayesian network on nodes $0, \dots, n-1$ and a set $L$ of latent nodes, the latent projection is the acyclic directed mixed graph on the observed nodes (those not in $L$) with a directed edge $i \to j$ when the network has a directed path from $i$ to $j$ whose interior nodes all lie in $L$, and a bidirected edge $i \leftrightarrow j$ when $i$ and $j$ have a latent common cause.
