# Cost of tail-recursive adjacent merging

Cost of merge_adj2 (accumulator version): only merge steps counted.
   Follows textbook convention that only calls/steps of `merge` are counted,
   so accumulator handling does not contribute to cost. Hence the required
   comparison `T_merge_adj2 acc ts = T_merge_adj ts` remains valid.
