# State space of the SIR chain in a population of size $N$

For a population size $N \in \mathbb{N}$, an SIR state is a pair $(S, I)$ of integers with
$0 \le S \le N$ and $0 \le I \le N$: the numbers of susceptible and infective individuals. The
constraint $S + I \le N$ is not part of the definition; the existence and absorption results for
the SIR chain assume it of the initial state. For a state with $S + I \le N$, the number of removed
individuals is $N - S - I$.
