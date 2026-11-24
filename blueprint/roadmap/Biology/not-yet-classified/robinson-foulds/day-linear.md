# Day's linear-time comparison

Hypotheses are two rooted trees on the
same `n` leaves (`hleaves`: labels biject onto leaves, i.e. every leaf
number occurs and labels are injective on labeled vertices), well-founded
parent links (`hwf`: every vertex reaches the root in fewer than `card`
steps), and a postorder numbering `σ` (`hpost`: every normalized cluster is
an interval). Conclusion: the table scan counts exactly the shared clusters.

## Sources

- Day (1985), via Briand et al. (2022).
