# Exception handler

For a value handler `g : α → β` and an exception handler `onRaise : E → β`,
`handle g onRaise` interprets an exception computation by sending `pure x` to
`g x` and each `raise e` to `onRaise e`, ignoring the continuation; it is the
fold of the free monad with these clauses.
