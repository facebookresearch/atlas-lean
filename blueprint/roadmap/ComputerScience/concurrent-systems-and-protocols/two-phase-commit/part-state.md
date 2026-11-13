# Participant states in two-phase commit

A participant is in one of four states: working
(it has not voted), prepared (it voted yes and waits for the decision), committed, or aborted
(it voted no, or learned of an abort).
