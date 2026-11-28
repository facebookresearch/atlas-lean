# The first overflow of a schedule

`firstOverflow tasks sched` is `some t` for the least time
`t` at which an overflow occurs, that is, the least deadline of a request that receives fewer than
`C` slots of work by its deadline, and `none` if no overflow ever occurs.
