# Count Run correct

The actual traced `count_run` evaluator returns a nonempty sorted natural
run, and its length is at least two unless exactly one input element remains.
Whole entries are permuted only within the returned range, and tagged
comparator-equivalent keys retain their canonical origin order.

The strict-weak-order and canonical-origin hypotheses are correctness-only:
the safety certificate remains the arbitrary-comparator `countRun_safe`
certificate, and exact erasure identifies both statements with one execution.
