# Output distribution in the random-oracle model

Let the domain $D$ have decidable equality (it need not be finite) and the range be a finite nonempty type. For an oracle algorithm $c$ with queries in $D$ and answers in the range, its output distribution in the random-oracle model is obtained by running $c$ against the lazily sampled random function from the empty table and keeping only the output marginal, discarding the final table (Katz and Lindell, Section 5.5.1).
