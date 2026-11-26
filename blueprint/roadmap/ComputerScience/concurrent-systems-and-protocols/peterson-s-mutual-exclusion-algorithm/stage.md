# Stages of a process in Peterson's algorithm

A process in Peterson's algorithm is at one of five stages: idle (outside the protocol, with its flag down); flag raised, about to assign the turn variable; waiting until the other flag is down or the turn variable favours it; in the critical section; and exiting, about to lower its flag after leaving the critical section.
