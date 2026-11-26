# Terms never decrease in Raft

For every sequence of steps from any state, the
`currentTerm` of every server stays the same or increases, crashes and recoveries included.
