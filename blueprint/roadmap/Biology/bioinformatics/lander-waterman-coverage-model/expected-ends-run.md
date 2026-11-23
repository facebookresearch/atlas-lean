# Expected number of run ends (exact)

Let $G$, $N$ and $V$ be natural numbers with $V + 1 \le G$ (so $G \ge 1$). Summed over the
positions $p \in \{0, \dots, G-1\}$, the [normalized counts](normalized-count.md) of the start
tuples in which $p$ is a [run end](ends-run.md) for the window $V$ add up to

$$G \Bigl(\bigl(1 - \tfrac{V}{G}\bigr)^N - \bigl(1 - \tfrac{V + 1}{G}\bigr)^N\Bigr).$$

When the $N$ start positions are independent and uniform on $\{0, \dots, G-1\}$, each normalized
count is the probability that $p$ is a run end, so this is the expected number of run-end
positions.
