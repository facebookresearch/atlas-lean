# Moulin pruning reaches the unique largest willing coalition

For every cross-monotonic scheme $\xi$ and arbitrary real bids $b$, the coalitions $S$ with $\xi(S, j) \le b_j$ for all $j \in S$ (willing coalitions) are closed under union, and Moulin's synchronous pruning terminates within $|A|$ rounds at the largest willing coalition. Moreover any finite sequence of valid partial deletions from $A$ that ends at a willing coalition ends at that same coalition.

## Proof sketch

Cross-monotonicity implies an agent willing in a coalition remains willing in every larger coalition (its share can only drop), so the union of willing coalitions is willing; pruning never removes an agent of the largest willing coalition, by induction on rounds.

## Depends on

- [Moulin's iterative-pruning mechanism](moulins-iterative-pruning-mechanism.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
