# Simulated annealing acceptance probability

For an energy $V$ on a finite state space, the probability of accepting a proposed move from $x$ to $y$ at temperature $T$ is
$$\min\Bigl(1,\ \exp\bigl(-\max(V(y) - V(x), 0)/T\bigr)\Bigr).$$
