# Merge Memory Lifecycle

Exact top-level shape: one initializer, zero or more directional calls,
and one terminal cleanup.  `events` is the evaluator's literal trace field;
there is no separately supplied history which could omit a call.
