# Events of an asynchronous message-passing system

In an event, the process `proc`
receives the multiset `delivered` of messages, each paired with its sender, and takes a step. It is
a delivery event if it delivers at least one message, and a computation event if `delivered`
is empty.
