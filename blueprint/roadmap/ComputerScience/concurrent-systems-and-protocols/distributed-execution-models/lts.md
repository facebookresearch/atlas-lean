# The transition system of an asynchronous message-passing system

An event `e` of process
`p` takes the configuration `C` to `C'` if, for every process `i`, the messages it delivers from
`i` form a sub-multiset of the channel `chan i p` of `C`, and `C'` is the result of applying `e`
to `C`.
