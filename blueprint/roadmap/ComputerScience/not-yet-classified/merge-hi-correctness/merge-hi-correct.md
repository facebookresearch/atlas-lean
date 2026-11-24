# Merge Hi correct

End-to-end functional correctness of the actual traced `merge_hi` call.

The shared semantic precondition records explicit nonemptiness, the two runs
under the public `Sorted` predicate, and both strict trimming endpoints needed
by the reverse evaluator.  Comparator binding and canonical stability remain
identical explicit premises of both merge-direction theorems.
