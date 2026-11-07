# The processes the detection algorithm lets finish

Given the free resource vector $w$ and a
list of pending processes, run the detection algorithm: repeatedly take the first pending process
whose request is at most what is free, let it finish, remove that entry from the list and add its
allocation to what is free, until no pending process has a request at most what is free. This is
the list of the processes taken, in the order they were taken.
