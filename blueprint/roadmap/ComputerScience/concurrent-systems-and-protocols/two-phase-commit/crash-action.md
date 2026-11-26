# Actions of two-phase commit with crashes

The actions of two-phase commit with crashes
over a set $P$ of participants are: a protocol action of two-phase commit; the coordinator times
out waiting for votes; a participant $p$ times out waiting for the vote request; a participant
$p$ asks a participant $q$ for the decision (cooperative termination); the coordinator crashes;
the coordinator recovers; a participant $p$ crashes; and a participant $p$ recovers.
