# The detection algorithm

Given the free resource vector $w$ and a list of pending
processes, repeatedly take the first pending process whose request is at most what is free, let it
finish, remove that entry from the list and add its allocation to what is free, until no pending
process has a request at most what is free. The processes still pending then are the ones reported
as deadlocked.
