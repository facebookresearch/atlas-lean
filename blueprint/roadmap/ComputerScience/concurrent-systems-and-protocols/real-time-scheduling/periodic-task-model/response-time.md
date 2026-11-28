# Response time of a request

The response time of request `k` of task `i` under a schedule is
`t` minus the time of the request, where `t` is the first time by which the request has received
`C` slots of work, the end of the slot in which it receives the last of them. Slots at or after the
deadline of the request do not count, so a request that receives fewer than `C` slots of work by its
deadline has no response time.
