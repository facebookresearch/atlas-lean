# Closed cohort extinct at time T: initial size equals deaths before T

Let $(P_t)$ and $(D_t)$ be real sequences indexed by the times $t \in \mathbb{N}$ with
$P_{t+1} = P_t - D_t$ for every $t$ (a closed cohort), and let $T \in \mathbb{N}$ be a time with
$P_T = 0$. Then $P_0 = \sum_{t < T} D_t$: the initial size of the cohort equals its total deaths at
the times $t = 0, \dots, T - 1$ before $T$. For $T = 0$ the sum is empty and the statement reads
$P_0 = 0$. No sign condition is needed, and $T$ need not be the first time at which the size is $0$.

Source: Methods Protocol for the Human Mortality Database, version 6, eq. (9).
