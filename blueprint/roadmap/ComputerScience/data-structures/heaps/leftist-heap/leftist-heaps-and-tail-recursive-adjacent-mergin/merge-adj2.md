# Tail-recursive adjacent merging with an accumulator

Tail-recursive merge_adj2 with accumulator, no use of List.append.
   Genuinely tail-recursive: uses an accumulator and reverse at base case.
   Does not use List.append (avoids append operator).
   Complexity model: only merge steps counted, so `T_merge_adj2 acc ts = T_merge_adj ts`
   should hold; accumulator reversal overhead is intentionally excluded
   per textbook convention that only merge calls are counted.
