# Storage Step

The atomic SC storage steps. Reads return shared memory and stores replace one shared value;
both require the lock to be free or held by the actor. A fence is inert even for a blocked
thread. Acquire needs a free lock and release needs ownership. There is no propagation step.
